import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6132027129:ℚ)/10000000000),((3317108299:ℚ)/5000000000),((8372027129:ℚ)/53400000000),((12511324897:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((126400653:ℚ)/200000000),((36337031786778785561729527021834598479733:ℚ)/2174741093376000000000000000000000000000000),((-345198329257223745762054023:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6607595141:ℚ)/10000000000),((1717978867:ℚ)/2500000000),((1263942163:ℚ)/7900000000),((6433936601:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5167682991:ℚ)/10000000000),((34973002683589058730022641275768181882002604370985792033861:ℚ)/2227353961556250000000000000000000000000000000000000000000000),((-120037524641329452994046581:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((3422674913:ℚ)/5000000000),((6990759859:ℚ)/10000000000),((504741657:ℚ)/3125000000),((3727468511:ℚ)/15800000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((898818393:ℚ)/2000000000),((376889898109333366164507044251772593625024381642653673:ℚ)/24651950000000000000000000000000000000000000000000000000),((-30633022392856925673535869:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((3482110353:ℚ)/5000000000),((1762545217:ℚ)/2500000000),((4602110353:ℚ)/28362500000),((6567635651:ℚ)/28125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((102985603:ℚ)/250000000),((10810379938182191158925056937475234467961287837453179978830373:ℚ)/715857538032531738281250000000000000000000000000000000000000000),((-92836196156664323994472727:ℚ)/1386240000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((3511827313:ℚ)/5000000000),((7109601111:ℚ)/10000000000),((4631827313:ℚ)/28600000000),((26448803333:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((979880577:ℚ)/2500000000),((8642572657403817938297607921817858061122738958683168270583:ℚ)/574225179201781250000000000000000000000000000000000000000000),((-31101726042781792124458269:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((1416617513:ℚ)/2000000000),((112015947:ℚ)/156250000),((621539171:ℚ)/3845000000),((37822531:ℚ)/162500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((927362479:ℚ)/2500000000),((178452342605090765933942186714155147613879795386145311:ℚ)/11894715426635742187500000000000000000000000000000000000),((-5001303395073424627603469:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((7142519549:ℚ)/10000000000),((3614219689:ℚ)/5000000000),((9382519549:ℚ)/58150000000),((13402659067:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3487365309:ℚ)/10000000000),((323427015605992822311256971403673646046047129644928910855303:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-125658637247741040576264101:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((7201950601:ℚ)/10000000000),((3643928719:ℚ)/5000000000),((9441950601:ℚ)/58625000000),((13491786157:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3250803121:ℚ)/10000000000),((3023409970276768810867589700806410338807938281404139180432057:ℚ)/202738450703828320312500000000000000000000000000000000000000000),((-126285061507944283157821901:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7261380743:ℚ)/10000000000),((1836818701:ℚ)/2500000000),((9501380743:ℚ)/59100000000),((6790456103:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((749082891:ℚ)/2500000000),((204407789524319855952828649043089595460323284245831248178961:ℚ)/13745279266826248168945312500000000000000000000000000000000000),((-126911857871587365382946349:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((7320809997:ℚ)/10000000000),((1481338299:ℚ)/2000000000),((9560809997:ℚ)/59575000000),((5468014897:ℚ)/23640000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((543784317:ℚ)/2000000000),((20862905524958469455926018432305218940602808452874459622646197:ℚ)/1406668536014302800000000000000000000000000000000000000000000000),((-382617079660133295720878927:ℚ)/5544960000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1476047677:ℚ)/2000000000),((298644301:ℚ)/400000000),((1924047677:ℚ)/12010000000),((1100732903:ℚ)/4766000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1205330713:ℚ)/5000000000),((902371531386574204773482682004362544769292866575011505889:ℚ)/60996956149139646875000000000000000000000000000000000000000),((-5126662710743535815406629:ℚ)/73932800000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((929958241:ℚ)/1250000000),((3792468833:ℚ)/5000000000),((19835381:ℚ)/125000000),((13937406499:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((514431559:ℚ)/2500000000),((20068541477353070413600682949084655757363946425963884573:ℚ)/1353377813281250000000000000000000000000000000000000000000),((-2012413776913880132990781:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3779259277:ℚ)/5000000000),((1007529339:ℚ)/1250000000),((4899259277:ℚ)/32400000000),((3662588017:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1045280573:ℚ)/10000000000),((551062894829162786036197606996599165354062616531550652431:ℚ)/36357967309570312500000000000000000000000000000000000000000),((-90063316187598350036989:ℚ)/1280000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((4016949467:ℚ)/5000000000),((2490285127:ℚ)/2500000000),((5136949467:ℚ)/40000000000),((8750855381:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((644170700257816632795220249053642380345835294176545409:ℚ)/39858075000000000000000000000000000000000000000000000000),((-9036737:ℚ)/128000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9935058777:ℚ)/10000000000),((3440550881:ℚ)/2500000000),((12175058777:ℚ)/110400000000),((11601652643:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1453912356988266549030705483657086645303:ℚ)/76176000000000000000000000000000000000000),((-9036737:ℚ)/128000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC19
#check @N11Formalization.C450NinthGroupedC19.bound
#print axioms N11Formalization.C450NinthGroupedC19.valid0
#print axioms N11Formalization.C450NinthGroupedC19.valid1
#print axioms N11Formalization.C450NinthGroupedC19.valid2
#print axioms N11Formalization.C450NinthGroupedC19.valid3
#print axioms N11Formalization.C450NinthGroupedC19.valid4
#print axioms N11Formalization.C450NinthGroupedC19.valid5
#print axioms N11Formalization.C450NinthGroupedC19.valid6
#print axioms N11Formalization.C450NinthGroupedC19.valid7
#print axioms N11Formalization.C450NinthGroupedC19.valid8
#print axioms N11Formalization.C450NinthGroupedC19.valid9
#print axioms N11Formalization.C450NinthGroupedC19.valid10
#print axioms N11Formalization.C450NinthGroupedC19.valid11
#print axioms N11Formalization.C450NinthGroupedC19.valid12
#print axioms N11Formalization.C450NinthGroupedC19.valid13
#print axioms N11Formalization.C450NinthGroupedC19.valid14
#print axioms N11Formalization.C450NinthGroupedC19.bound
#print axioms N11Formalization.C450NinthGroupedC19.endpoint_checks
