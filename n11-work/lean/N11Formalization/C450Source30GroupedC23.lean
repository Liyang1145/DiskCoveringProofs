import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((5604124679:ℚ)/10000000000),((5933220151:ℚ)/10000000000),((25772374037:ℚ)/51500000000),((60092541057:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7416058141:ℚ)/10000000000),((-495218367639017630534568571948476445495777034500338344668477:ℚ)/2087986995200000000000000000000000000000000000000000000000000),((-1131134918489455929231366237:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((5844929651:ℚ)/10000000000),((6173756519:ℚ)/10000000000),((26494788953:ℚ)/53400000000),((61776295633:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6934119597:ℚ)/10000000000),((-9508734796650319324337098485260741432980328693544959839379561:ℚ)/40572612032812500000000000000000000000000000000000000000000000),((-1128191207587526036832600957:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6085494859:ℚ)/10000000000),((393371477:ℚ)/625000000),((27216484577:ℚ)/54350000000),((3913600339:ℚ)/6675000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3211475631:ℚ)/5000000000),((-19279665800523507879189984068777165904549398959233224191483:ℚ)/81344679332128906250000000000000000000000000000000000000000),((-4437966262068712253541973:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6205695609:ℚ)/10000000000),((12828161:ℚ)/20000000),((27577086827:ℚ)/55300000000),((126917127:ℚ)/217400000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3077032067:ℚ)/5000000000),((-72310301116608918523847201672188062210849614096240933:ℚ)/306851976646036718750000000000000000000000000000000000),((-4536348536912454875597:ℚ)/11829248000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((1581461407:ℚ)/2500000000),((6534169727:ℚ)/10000000000),((6984384221:ℚ)/14062500000),((64299188089:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1174930989:ℚ)/2000000000),((-208996324399711510620592308233849420965016574724898776793:ℚ)/891803550585937500000000000000000000000000000000000000000),((-1131833212984093957052032973:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((3222973773:ℚ)/5000000000),((332710687:ℚ)/500000000),((1088378563:ℚ)/2200000000),((3256974809:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5583111563:ℚ)/10000000000),((-387354994478808157617374962256761434022573920084222259:ℚ)/1661682128906250000000000000000000000000000000000000000),((-2823394569650040324602253:ℚ)/7393280000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1313200763:ℚ)/2000000000),((6774214801:ℚ)/10000000000),((5731602289:ℚ)/11630000000),((65979503607:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1055478019:ℚ)/2000000000),((-266850347571967191270485817838256859368046766436667838849991303:ℚ)/1150601232809600000000000000000000000000000000000000000000000000),((-1126661192118295391732297837:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3343008359:ℚ)/5000000000),((430885939:ℚ)/625000000),((14509025077:ℚ)/29550000000),((4176201573:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4954832633:ℚ)/10000000000),((-16123678907001467845545191342104659638630915717654850360949:ℚ)/69863916690814590454101562500000000000000000000000000000000),((-4389623063458139920868277:ℚ)/11552000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((850748549:ℚ)/1250000000),((7133980741:ℚ)/10000000000),((3672245647:ℚ)/7625000000),((22832621729:ℚ)/39400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((461187251:ℚ)/1000000000),((-320497583884011979124078460402053281621864797207524919322099:ℚ)/1422421646650000000000000000000000000000000000000000000000000),((-1107537890278445240899006597:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1761453977:ℚ)/2500000000),((7613181191:ℚ)/10000000000),((7524361931:ℚ)/16200000000),((71852268337:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((960617003:ℚ)/2500000000),((-5350519659121679905181214979713503353514613227618236970312921:ℚ)/24820372350000000000000000000000000000000000000000000000000000),((-44163329223233343:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((376252801:ℚ)/500000000),((4762976977:ℚ)/5000000000),((1576758403:ℚ)/4000000000),((42620838839:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((351377637:ℚ)/2500000000),((-11106175773528310750683015358149234777228615390363970927:ℚ)/62985600000000000000000000000000000000000000000000000000),((-481667149218861:ℚ)/1280000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((471897451:ℚ)/500000000),((6670443301:ℚ)/5000000000),((1863692353:ℚ)/5520000000),((55973103107:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-182298797020965068242969887894826704591334536531770582380811:ℚ)/1269600000000000000000000000000000000000000000000000000000000),((-387434227:ℚ)/1024000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC23
#check @N11Formalization.C450Source30GroupedC23.bound
#print axioms N11Formalization.C450Source30GroupedC23.valid0
#print axioms N11Formalization.C450Source30GroupedC23.valid1
#print axioms N11Formalization.C450Source30GroupedC23.valid2
#print axioms N11Formalization.C450Source30GroupedC23.valid3
#print axioms N11Formalization.C450Source30GroupedC23.valid4
#print axioms N11Formalization.C450Source30GroupedC23.valid5
#print axioms N11Formalization.C450Source30GroupedC23.valid6
#print axioms N11Formalization.C450Source30GroupedC23.valid7
#print axioms N11Formalization.C450Source30GroupedC23.valid8
#print axioms N11Formalization.C450Source30GroupedC23.valid9
#print axioms N11Formalization.C450Source30GroupedC23.valid10
#print axioms N11Formalization.C450Source30GroupedC23.valid11
#print axioms N11Formalization.C450Source30GroupedC23.bound
#print axioms N11Formalization.C450Source30GroupedC23.endpoint_checks
