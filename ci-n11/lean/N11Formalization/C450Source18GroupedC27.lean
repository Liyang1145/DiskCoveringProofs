import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((2856401947:ℚ)/5000000000),((1251255423:ℚ)/2000000000),((1122800649:ℚ)/1780000000),((15939809653:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7201834949:ℚ)/10000000000),((-19201590770867555251214863467121:ℚ)/704969000000000000000000000000000),((-240600664013096965609583:ℚ)/739328000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6189209489:ℚ)/10000000000),((3247211057:ℚ)/5000000000),((7213209489:ℚ)/11060000000),((41159321627:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((619154089:ℚ)/1000000000),((-1882862864391154884576384000528142981874553691025997:ℚ)/53516575000000000000000000000000000000000000000000000),((-1504134579638652981674223:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6427339553:ℚ)/10000000000),((67325241:ℚ)/100000000),((7451339553:ℚ)/11440000000),((849377651:ℚ)/1106000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5629159991:ℚ)/10000000000),((-166353745514641656804403475746065774686620566023991851:ℚ)/4678731200000000000000000000000000000000000000000000000),((-601163250925185759287:ℚ)/1848320000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1333085521:ℚ)/2000000000),((6851560287:ℚ)/10000000000),((1537885521:ℚ)/2326000000),((86247163157:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2505757227:ℚ)/5000000000),((-383147708634592064712398683023915092719310001327027:ℚ)/9831485918750000000000000000000000000000000000000000),((-6012047537861503460812463:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6784457169:ℚ)/10000000000),((3485293621:ℚ)/5000000000),((7808457169:ℚ)/11820000000),((43778229831:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4675132781:ℚ)/10000000000),((-151059426395847541476820411664855967817438204331164841:ℚ)/3870470081250000000000000000000000000000000000000000000),((-1502337198586174367630807:ℚ)/4620800000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3451738857:ℚ)/5000000000),((7089605403:ℚ)/10000000000),((3963738857:ℚ)/6005000000),((88865659433:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4314691321:ℚ)/10000000000),((-79321521575656246139762124840566862612402823962610873:ℚ)/2030066719921875000000000000000000000000000000000000000),((-6006551848557039637963543:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((7022489671:ℚ)/10000000000),((1441723037:ℚ)/2000000000),((8046489671:ℚ)/12200000000),((18034953407:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3923533091:ℚ)/10000000000),((-221908260530082241523166695065551027266656718709070317:ℚ)/5674525000000000000000000000000000000000000000000000000),((-240146268497857856679463:ℚ)/739328000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7141493443:ℚ)/10000000000),((3663808487:ℚ)/5000000000),((8165493443:ℚ)/12390000000),((45741893357:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((872828571:ℚ)/2500000000),((-2153378852638525377653542213467492284381387796111667:ℚ)/55035153906250000000000000000000000000000000000000000),((-1500165849338469161596063:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7260489407:ℚ)/10000000000),((3723305567:ℚ)/5000000000),((8284489407:ℚ)/12580000000),((46396361237:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((600060471:ℚ)/2000000000),((-237786679370774493554830089375260857983329580748189:ℚ)/6075639379882812500000000000000000000000000000000000),((-1499392978455501534458703:ℚ)/4620800000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7379477919:ℚ)/10000000000),((3842288957:ℚ)/5000000000),((8403477919:ℚ)/12960000000),((47705178527:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2414849119:ℚ)/10000000000),((-9163774886762444611229366026457275173956894551271311:ℚ)/251942400000000000000000000000000000000000000000000000),((-157699218806548291:ℚ)/486400000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7617433903:ℚ)/10000000000),((1917502441:ℚ)/2000000000),((8641433903:ℚ)/16000000000),((7756175617:ℚ)/8640000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-21600497520971787858902919656675775204154723248337903:ℚ)/2400000000000000000000000000000000000000000000000000000),((-20769239:ℚ)/64000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((595018773:ℚ)/625000000),((13390953559:ℚ)/10000000000),((659018773:ℚ)/1380000000),((158180489149:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((10188458674490815878161:ℚ)/952200000000000000000000),((-20769239:ℚ)/64000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC27
#check @N11Formalization.C450Source18GroupedC27.bound
#print axioms N11Formalization.C450Source18GroupedC27.valid0
#print axioms N11Formalization.C450Source18GroupedC27.valid1
#print axioms N11Formalization.C450Source18GroupedC27.valid2
#print axioms N11Formalization.C450Source18GroupedC27.valid3
#print axioms N11Formalization.C450Source18GroupedC27.valid4
#print axioms N11Formalization.C450Source18GroupedC27.valid5
#print axioms N11Formalization.C450Source18GroupedC27.valid6
#print axioms N11Formalization.C450Source18GroupedC27.valid7
#print axioms N11Formalization.C450Source18GroupedC27.valid8
#print axioms N11Formalization.C450Source18GroupedC27.valid9
#print axioms N11Formalization.C450Source18GroupedC27.valid10
#print axioms N11Formalization.C450Source18GroupedC27.valid11
#print axioms N11Formalization.C450Source18GroupedC27.bound
#print axioms N11Formalization.C450Source18GroupedC27.endpoint_checks
