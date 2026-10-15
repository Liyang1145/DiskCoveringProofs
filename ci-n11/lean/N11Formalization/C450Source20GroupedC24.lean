import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5784965529:ℚ)/10000000000),((6328526927:ℚ)/10000000000),((17338252901:ℚ)/35600000000),((7848526927:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3528330907:ℚ)/5000000000),((2009734615538973129448051:ℚ)/158420000000000000000000000),((-4875517428159583645505107:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((62624713:ℚ)/100000000),((6567113141:ℚ)/10000000000),((553572991:ℚ)/1106000000),((8087113141:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6023447861:ℚ)/10000000000),((81613960196626888297889369178986640853210253425277:ℚ)/12683428275000000000000000000000000000000000000000000),((-4965280454296548708791323:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((1300218823:ℚ)/2000000000),((6805626731:ℚ)/10000000000),((877348597:ℚ)/1760000000),((8325626731:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2722299919:ℚ)/5000000000),((22477047349182315522461680396711:ℚ)/3872000000000000000000000000000000),((-5000142018893449117267163:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3369820921:ℚ)/5000000000),((3462429267:ℚ)/5000000000),((29348746447:ℚ)/58150000000),((4222429267:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((600541007:ℚ)/1250000000),((1521407655866733154717408262674162941468429985581587741:ℚ)/460850902441406250000000000000000000000000000000000000000),((-3783284625018511492047361:ℚ)/10830000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1714722467:ℚ)/2500000000),((3522037379:ℚ)/5000000000),((14883057269:ℚ)/29550000000),((4282037379:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1113226659:ℚ)/2500000000),((189993942978261505668635222360461116023248709035214407:ℚ)/60476095019531250000000000000000000000000000000000000000),((-1265342286578626628275403:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3489060893:ℚ)/5000000000),((1432655229:ℚ)/2000000000),((30183426251:ℚ)/60050000000),((1736655229:ℚ)/2955000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4073499923:ℚ)/10000000000),((6105928723047956662309987587706313109437167790253549697:ℚ)/2030066719921875000000000000000000000000000000000000000000),((-609382133024441350653409:ℚ)/1732800000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1419467673:ℚ)/2000000000),((1456492679:ℚ)/2000000000),((12240273711:ℚ)/24400000000),((1760492679:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3657373489:ℚ)/10000000000),((131574605115754924369411031038951853934311079994418839:ℚ)/45396200000000000000000000000000000000000000000000000000),((-203793022549904704369603:ℚ)/577600000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((902067541:ℚ)/1250000000),((7401637163:ℚ)/10000000000),((7754472787:ℚ)/15487500000),((8921637163:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3190150819:ℚ)/10000000000),((2720656337844786926167480084681376642303516966679449:ℚ)/967414814758300781250000000000000000000000000000000000),((-5111292678545875299928027:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((7335728353:ℚ)/10000000000),((7520798063:ℚ)/10000000000),((62870098471:ℚ)/125800000000),((9040798063:ℚ)/15487500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2644843931:ℚ)/10000000000),((1699065396585415005791808078154029:ℚ)/618189062500000000000000000000000000),((-269872944347228308898433:ℚ)/760000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((1863725769:ℚ)/2500000000),((3879541771:ℚ)/5000000000),((589854829:ℚ)/1200000000),((4639541771:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((978589817:ℚ)/5000000000),((8067186807992372797802094019081:ℚ)/1800000000000000000000000000000000),((-1354576014649097:ℚ)/3800000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((769321497:ℚ)/1000000000),((9664019243:ℚ)/10000000000),((6537250479:ℚ)/16000000000),((11184019243:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5553104503968727977409696262342083:ℚ)/240000000000000000000000000000000000),((-89687:ℚ)/250000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((9598316489:ℚ)/10000000000),((1683725517:ℚ)/1250000000),((78708215423:ℚ)/220800000000),((1873725517:ℚ)/2500000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((260928002828500142301579179:ℚ)/6094080000000000000000000000),((-89687:ℚ)/250000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC24
#check @N11Formalization.C450Source20GroupedC24.bound
#print axioms N11Formalization.C450Source20GroupedC24.valid0
#print axioms N11Formalization.C450Source20GroupedC24.valid1
#print axioms N11Formalization.C450Source20GroupedC24.valid2
#print axioms N11Formalization.C450Source20GroupedC24.valid3
#print axioms N11Formalization.C450Source20GroupedC24.valid4
#print axioms N11Formalization.C450Source20GroupedC24.valid5
#print axioms N11Formalization.C450Source20GroupedC24.valid6
#print axioms N11Formalization.C450Source20GroupedC24.valid7
#print axioms N11Formalization.C450Source20GroupedC24.valid8
#print axioms N11Formalization.C450Source20GroupedC24.valid9
#print axioms N11Formalization.C450Source20GroupedC24.valid10
#print axioms N11Formalization.C450Source20GroupedC24.valid11
#print axioms N11Formalization.C450Source20GroupedC24.bound
#print axioms N11Formalization.C450Source20GroupedC24.endpoint_checks
