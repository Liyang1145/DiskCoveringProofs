import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((373132597:ℚ)/625000000),((6499671047:ℚ)/10000000000),((523132597:ℚ)/1668750000),((8547671047:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1668060773:ℚ)/2500000000),((2527894450789508369543062511122756658987:ℚ)/69591714988032000000000000000000000000000),((-661344636067636828171425253:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6447256951:ℚ)/10000000000),((3369022223:ℚ)/5000000000),((8847256951:ℚ)/27650000000),((1464340741:ℚ)/3560000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5579858453:ℚ)/10000000000),((4205547736650311044489553905552448614170167836873351201841:ℚ)/129351518952600000000000000000000000000000000000000000000000),((-171354383220395970985195093:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3342856961:ℚ)/5000000000),((3428604451:ℚ)/5000000000),((4542856961:ℚ)/14062500000),((4452604451:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1238917633:ℚ)/2500000000),((1511659140079423744204906598645208170783893746578228771:ℚ)/48921794775000000000000000000000000000000000000000000000),((-174358116963383770503777117:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((850614753:ℚ)/1250000000),((3488179761:ℚ)/5000000000),((1150614753:ℚ)/3575000000),((4512179761:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1153759079:ℚ)/2500000000),((253392531373530966492884228957413546368781136461017333533:ℚ)/8271551513671875000000000000000000000000000000000000000000),((-527346361451099724744851071:ℚ)/2217984000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6924106959:ℚ)/10000000000),((1773874247:ℚ)/2500000000),((9324106959:ℚ)/29075000000),((2285874247:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((531165193:ℚ)/1250000000),((18033723507840091032200209824544406024665195078481909367323:ℚ)/593278760667450000000000000000000000000000000000000000000000),((-44300828537720529949658853:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((281731259:ℚ)/400000000),((3607310969:ℚ)/5000000000),((377731259:ℚ)/1182000000),((4631310969:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((770270859:ℚ)/2000000000),((1439659221130463381876006819630863822919030875450839137927:ℚ)/47693767127596093750000000000000000000000000000000000000000),((-178621707875459836878353637:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((223826321:ℚ)/312500000),((733373497:ℚ)/1000000000),((298826321:ℚ)/938281250),((312724499:ℚ)/788000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((68196467:ℚ)/200000000),((198492755819443399080569497382903939229347211370036440511:ℚ)/6616616196343800000000000000000000000000000000000000000000),((-7201492437244003848522853:ℚ)/29573120000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((3640795003:ℚ)/5000000000),((1863209161:ℚ)/2500000000),((4840795003:ℚ)/15250000000),((2375209161:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2904889379:ℚ)/10000000000),((75126810720051660373794731596285005399210353547384431503:ℚ)/2517959421609765625000000000000000000000000000000000000000),((-45362533002292820688605957:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1850181323:ℚ)/2500000000),((7691007989:ℚ)/10000000000),((2450181323:ℚ)/7862500000),((9739007989:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((459005437:ℚ)/2000000000),((137076231336554675601338454090234111851250697443510232478627:ℚ)/4490149491050000000000000000000000000000000000000000000000000),((-12027682924953241:ℚ)/48640000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3819480393:ℚ)/5000000000),((247785619:ℚ)/312500000),((1673160131:ℚ)/5400000000),((311785619:ℚ)/786250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((33527065436858337524057927490853912262827002402374737:ℚ)/1107285276983642578125000000000000000000000000000000000),((-256864531:ℚ)/1024000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((7877152961:ℚ)/10000000000),((491655537:ℚ)/500000000),((10277152961:ℚ)/40000000000),((594055537:ℚ)/1296000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((49158154664195659565714318428438340309270160980333:ℚ)/1275458400000000000000000000000000000000000000000000),((-256864531:ℚ)/1024000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((978150289:ℚ)/1000000000),((13637766319:ℚ)/10000000000),((1218150289:ℚ)/5520000000),((15685766319:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((986666464709000445116829652872754314979:ℚ)/19501056000000000000000000000000000000000),((-256864531:ℚ)/1024000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC21
#check @N11Formalization.C450Source17GroupedC21.bound
#print axioms N11Formalization.C450Source17GroupedC21.valid0
#print axioms N11Formalization.C450Source17GroupedC21.valid1
#print axioms N11Formalization.C450Source17GroupedC21.valid2
#print axioms N11Formalization.C450Source17GroupedC21.valid3
#print axioms N11Formalization.C450Source17GroupedC21.valid4
#print axioms N11Formalization.C450Source17GroupedC21.valid5
#print axioms N11Formalization.C450Source17GroupedC21.valid6
#print axioms N11Formalization.C450Source17GroupedC21.valid7
#print axioms N11Formalization.C450Source17GroupedC21.valid8
#print axioms N11Formalization.C450Source17GroupedC21.valid9
#print axioms N11Formalization.C450Source17GroupedC21.valid10
#print axioms N11Formalization.C450Source17GroupedC21.valid11
#print axioms N11Formalization.C450Source17GroupedC21.bound
#print axioms N11Formalization.C450Source17GroupedC21.endpoint_checks
