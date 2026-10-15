import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5737285347:ℚ)/10000000000),((3138800423:ℚ)/5000000000),((72070138817:ℚ)/106800000000),((10616401269:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7152855993:ℚ)/10000000000),((-140431755496151982201899450152377373:ℚ)/3806832600000000000000000000000000000),((-56511151877134065131596191:ℚ)/194560000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((31065959:ℚ)/50000000),((6515527609:ℚ)/10000000000),((386525549:ℚ)/553000000),((7315527609:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3068478867:ℚ)/5000000000),((-1750669208962860051294784856581035348289564972481:ℚ)/39635713359375000000000000000000000000000000000000),((-225417735074749367925944799:ℚ)/778240000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6451098189:ℚ)/10000000000),((6753425949:ℚ)/10000000000),((79922080079:ℚ)/114400000000),((22660277847:ℚ)/27650000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5570305409:ℚ)/10000000000),((-399764647635048573879854312631242727626452348709524061:ℚ)/8997560000000000000000000000000000000000000000000000000),((-35492268298942628950930423:ℚ)/122880000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1337795503:ℚ)/2000000000),((1374473067:ℚ)/2000000000),((16507750533:ℚ)/23260000000),((4603419201:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2473316319:ℚ)/5000000000),((-11704209629632779472615737954357731332372122110932691:ℚ)/245787147968750000000000000000000000000000000000000000),((-26935829208664113283916293:ℚ)/93388800000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3403953931:ℚ)/5000000000),((6991298617:ℚ)/10000000000),((13974497747:ℚ)/19700000000),((23373895851:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2303096933:ℚ)/5000000000),((-21345658362531402384312571591943456241166077863862623:ℚ)/447971074218750000000000000000000000000000000000000000),((-224144494881398625871915231:ℚ)/778240000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6926832397:ℚ)/10000000000),((7110226087:ℚ)/10000000000),((85155156367:ℚ)/120100000000),((7910226087:ℚ)/9850000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((8481229:ℚ)/20000000),((-19355927171113182283951973292405583555245195980507544907:ℚ)/406013343984375000000000000000000000000000000000000000000),((-223822119780233624895982751:ℚ)/778240000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3522875699:ℚ)/5000000000),((7169687729:ℚ)/10000000000),((43231632689:ℚ)/60525000000),((23909063187:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3842694441:ℚ)/10000000000),((-94582332384047068455836157565988379810845896657963423:ℚ)/1924650670166015625000000000000000000000000000000000000),((-223660322102835889765781039:ℚ)/778240000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((1421041781:ℚ)/2000000000),((3614574009:ℚ)/5000000000),((17423459591:ℚ)/24400000000),((4014574009:ℚ)/5043750000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3628306557:ℚ)/10000000000),((-55762862386255191049546087485408049103054002722924113:ℚ)/1134905000000000000000000000000000000000000000000000000),((-167623588197849452469776797:ℚ)/583680000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((57317321:ℚ)/80000000),((918508083:ℚ)/1250000000),((702170531:ℚ)/991200000),((3055524249:ℚ)/3812500000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1700533227:ℚ)/5000000000),((-302426025049355063106857942266320596590036521911:ℚ)/6340049730000000000000000000000000000000000000000),((-10461210368637120306727093:ℚ)/36480000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((364178691:ℚ)/500000000),((3733488133:ℚ)/5000000000),((4453965601:ℚ)/6290000000),((4133488133:ℚ)/5162500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((361970249:ℚ)/1250000000),((-53279959251512916378218743913323755653119548431:ℚ)/1116845474243164062500000000000000000000000000000),((-55711307533900866760842231:ℚ)/194560000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((462654857:ℚ)/625000000),((1926196307:ℚ)/2500000000),((1883067809:ℚ)/2700000000),((375211113:ℚ)/462500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2284869347:ℚ)/10000000000),((-2566132105541509900450724173758373924831645719509:ℚ)/56953125000000000000000000000000000000000000000000),((-292733143:ℚ)/1024000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((3820135967:ℚ)/5000000000),((9606727831:ℚ)/10000000000),((46501495637:ℚ)/80000000000),((3468909277:ℚ)/3600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-140527273649261821198381431022614129440431879880316833:ℚ)/7500000000000000000000000000000000000000000000000000000),((-292733143:ℚ)/1024000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((4771060947:ℚ)/5000000000),((13409006853:ℚ)/10000000000),((56961670417:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6787847173805212590842428924778573:ℚ)/4204915200000000000000000000000000000),((-292733143:ℚ)/1024000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC28
#check @N11Formalization.C450Source16GroupedC28.bound
#print axioms N11Formalization.C450Source16GroupedC28.valid0
#print axioms N11Formalization.C450Source16GroupedC28.valid1
#print axioms N11Formalization.C450Source16GroupedC28.valid2
#print axioms N11Formalization.C450Source16GroupedC28.valid3
#print axioms N11Formalization.C450Source16GroupedC28.valid4
#print axioms N11Formalization.C450Source16GroupedC28.valid5
#print axioms N11Formalization.C450Source16GroupedC28.valid6
#print axioms N11Formalization.C450Source16GroupedC28.valid7
#print axioms N11Formalization.C450Source16GroupedC28.valid8
#print axioms N11Formalization.C450Source16GroupedC28.valid9
#print axioms N11Formalization.C450Source16GroupedC28.valid10
#print axioms N11Formalization.C450Source16GroupedC28.valid11
#print axioms N11Formalization.C450Source16GroupedC28.valid12
#print axioms N11Formalization.C450Source16GroupedC28.bound
#print axioms N11Formalization.C450Source16GroupedC28.endpoint_checks
