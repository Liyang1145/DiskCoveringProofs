import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((95315529:ℚ)/156250000),((3303797573:ℚ)/5000000000),((365946587:ℚ)/1668750000),((4023797573:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6390594651:ℚ)/10000000000),((499929370607317482378986113905215299451:ℚ)/33980329584000000000000000000000000000000),((-312929290783560487348977:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6575892661:ℚ)/10000000000),((6845349831:ℚ)/10000000000),((24847677983:ℚ)/110600000000),((2761783277:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((525149433:ℚ)/1000000000),((54704396926075460272020255443135756372110831096219991929291:ℚ)/4042234967268750000000000000000000000000000000000000000000000),((-1325693554286246131659195737:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6813705977:ℚ)/10000000000),((6964220711:ℚ)/10000000000),((25561117931:ℚ)/112500000000),((8404220711:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4589000863:ℚ)/10000000000),((2848029130028926395759045788961580673754132191107615691:ℚ)/218400869531250000000000000000000000000000000000000000000),((-1347718641715975575927072913:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((6932604683:ℚ)/10000000000),((7023654631:ℚ)/10000000000),((25917814049:ℚ)/113450000000),((8463654631:ℚ)/28125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4222117913:ℚ)/10000000000),((9173623977225365575588492938756877483340282129103497428346899:ℚ)/715857538032531738281250000000000000000000000000000000000000000),((-1358745653745205022019715033:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((1748013041:ℚ)/2500000000),((708308757:ℚ)/1000000000),((6524039123:ℚ)/28600000000),((852308757:ℚ)/2836250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1006745821:ℚ)/2500000000),((1489026930246400484616890129783014690785080239134138933:ℚ)/116639489525361816406250000000000000000000000000000000000),((-85266424188331267545435457:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((176287461:ℚ)/250000000),((3571259777:ℚ)/5000000000),((656862383:ℚ)/2883750000),((4291259777:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1911236227:ℚ)/5000000000),((103103688749293961221558971764608255932427431332860556115199:ℚ)/8105915511220312500000000000000000000000000000000000000000000),((-856113963894405370298937:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7110943539:ℚ)/10000000000),((3600975303:ℚ)/5000000000),((26452830617:ℚ)/116300000000),((1440325101:ℚ)/4806250000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1803493439:ℚ)/5000000000),((475857651239704021087804553424307999457680878826894856049:ℚ)/37542095451569885253906250000000000000000000000000000000000),((-1375304321845944459523244937:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((7170387491:ℚ)/10000000000),((1815345187:ℚ)/2500000000),((26631162473:ℚ)/117250000000),((2175345187:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1689211459:ℚ)/5000000000),((5002430046726174934202070660365380553102468533792666446221:ℚ)/395973536530914688110351562500000000000000000000000000000000),((-1380828728496171099048713257:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1807457581:ℚ)/2500000000),((3660405001:ℚ)/5000000000),((6702372743:ℚ)/29550000000),((625772143:ℚ)/2093750000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((97934869:ℚ)/312500000),((63082548034556488322194465053969208109803327326081304643:ℚ)/5009212560796737670898437500000000000000000000000000000000),((-86647222789939489661503817:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((1457854413:ℚ)/2000000000),((738023839:ℚ)/1000000000),((5397563239:ℚ)/23830000000),((882023839:ℚ)/2955000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2869387857:ℚ)/10000000000),((34494812125067855584220885961508620866017799871958383863513:ℚ)/2747399484402935156250000000000000000000000000000000000000000),((-55675393305742596892262793:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((367435637:ℚ)/500000000),((7439665933:ℚ)/10000000000),((1358306911:ℚ)/6005000000),((8879665933:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1289339811:ℚ)/5000000000),((186439712581745388043104068528024366699896928253709316750337:ℚ)/14891834997348546600341796875000000000000000000000000000000000),((-3493541336975825590399193:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((3704076187:ℚ)/5000000000),((7558518559:ℚ)/10000000000),((13672228561:ℚ)/61000000000),((8998518559:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2251667467:ℚ)/10000000000),((129962685742767885908166560942813055526338169249355314359:ℚ)/10319505826269531250000000000000000000000000000000000000000),((-350737668317798992439009593:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3763514309:ℚ)/5000000000),((7796214501:ℚ)/10000000000),((13850542927:ℚ)/62900000000),((9236214501:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1386859901:ℚ)/10000000000),((223397162841611410854969577595054266823728904815182093317321:ℚ)/17539646449414062500000000000000000000000000000000000000000000),((-353506566982702581728696057:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7764769647:ℚ)/10000000000),((8033898939:ℚ)/10000000000),((28414308941:ℚ)/129600000000),((9473898939:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((16100818447054863788470108919474047263306094982865142072711:ℚ)/1275592639085156250000000000000000000000000000000000000000000),((-98395427:ℚ)/1024000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((4001248261:ℚ)/5000000000),((4967529391:ℚ)/5000000000),((14563744783:ℚ)/80000000000),((5687529391:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((73385742944234774921793006292470559092536270886646697:ℚ)/4982259375000000000000000000000000000000000000000000000),((-98395427:ℚ)/1024000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9903923151:ℚ)/10000000000),((3434104957:ℚ)/2500000000),((34831769453:ℚ)/220800000000),((3794104957:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((21659038953218270331075509322503487971:ℚ)/1190250000000000000000000000000000000000),((-98395427:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC20
#check @N11Formalization.C450TenthGroupedC20.bound
#print axioms N11Formalization.C450TenthGroupedC20.valid0
#print axioms N11Formalization.C450TenthGroupedC20.valid1
#print axioms N11Formalization.C450TenthGroupedC20.valid2
#print axioms N11Formalization.C450TenthGroupedC20.valid3
#print axioms N11Formalization.C450TenthGroupedC20.valid4
#print axioms N11Formalization.C450TenthGroupedC20.valid5
#print axioms N11Formalization.C450TenthGroupedC20.valid6
#print axioms N11Formalization.C450TenthGroupedC20.valid7
#print axioms N11Formalization.C450TenthGroupedC20.valid8
#print axioms N11Formalization.C450TenthGroupedC20.valid9
#print axioms N11Formalization.C450TenthGroupedC20.valid10
#print axioms N11Formalization.C450TenthGroupedC20.valid11
#print axioms N11Formalization.C450TenthGroupedC20.valid12
#print axioms N11Formalization.C450TenthGroupedC20.valid13
#print axioms N11Formalization.C450TenthGroupedC20.valid14
#print axioms N11Formalization.C450TenthGroupedC20.valid15
#print axioms N11Formalization.C450TenthGroupedC20.bound
#print axioms N11Formalization.C450TenthGroupedC20.endpoint_checks
