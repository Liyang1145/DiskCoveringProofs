import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5861234243:ℚ)/10000000000),((799150251:ℚ)/1250000000),((14529546567:ℚ)/17800000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6900486731:ℚ)/10000000000),((-287036871812106746029612251402188263:ℚ)/8812112500000000000000000000000000000),((-9214974440387193722074353:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1584081083:ℚ)/2500000000),((6630763799:ℚ)/10000000000),((11728567581:ℚ)/13825000000),((7014763799:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((292486599:ℚ)/500000000),((-86405250000797812097124421043731203147312534301792737:ℚ)/2359268652343750000000000000000000000000000000000000000),((-585944842871561883240012553:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((1643466183:ℚ)/2500000000),((6749543129:ℚ)/10000000000),((12144263281:ℚ)/14062500000),((21400629387:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2628407127:ℚ)/5000000000),((-223357088588302918098889872952663377182236999420493057:ℚ)/5793571472167968750000000000000000000000000000000000000),((-584035371099230629230391273:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6692633909:ℚ)/10000000000),((1717080371:ℚ)/2500000000),((49408437363:ℚ)/57200000000),((1813080371:ℚ)/1875000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((617061117:ℚ)/1250000000),((-4098040084358186632822636783161589228202281111397842627:ℚ)/106334800000000000000000000000000000000000000000000000000),((-36382755679692349838002273:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((425712653:ℚ)/625000000),((218346841:ℚ)/312500000),((3139988571:ℚ)/3634375000),((691040523:ℚ)/715000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4595838609:ℚ)/10000000000),((-2889879371517507200302737284721585643032663826444849:ℚ)/75008284902572631835937500000000000000000000000000000),((-1569563174857551976513:ℚ)/8000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((3465085191:ℚ)/5000000000),((7046487293:ℚ)/10000000000),((25535596337:ℚ)/29312500000),((22291461879:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4229927601:ℚ)/10000000000),((-2660214839447017025970929822028887434936378828998162623:ℚ)/67462403869628906250000000000000000000000000000000000000),((-579253778103195047764965697:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((698955413:ℚ)/1000000000),((3552937729:ℚ)/5000000000),((1716229297:ℚ)/1970000000),((11234813187:ℚ)/11725000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1008840513:ℚ)/2500000000),((-470892630203615730401870895190896158683119581370363:ℚ)/11945895312500000000000000000000000000000000000000000),((-144574025550625780428471673:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3524468869:ℚ)/5000000000),((3582631707:ℚ)/5000000000),((25951282083:ℚ)/29787500000),((3774631707:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((383149527:ℚ)/1000000000),((-6509404455818748507584341356929976056304951794045326473:ℚ)/165189402917480468750000000000000000000000000000000000000),((-144334493415120365271863697:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7108321209:ℚ)/10000000000),((1806162791:ℚ)/2500000000),((52318248463:ℚ)/60050000000),((5706488373:ℚ)/5957500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((904187709:ℚ)/2500000000),((-39985516120582383932862350679408600184049643754003269751:ℚ)/1015033359960937500000000000000000000000000000000000000000),((-36023712027094362007852393:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3583852273:ℚ)/5000000000),((1456807743:ℚ)/2000000000),((2929662879:ℚ)/3362500000),((4600823229:ℚ)/4804000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((677811501:ℚ)/2000000000),((-2339375222784419098648596209273786834120259944840229:ℚ)/59402798461914062500000000000000000000000000000000000),((-23016814336530614900994297:ℚ)/118292480000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((903385969:ℚ)/1250000000),((734342607:ℚ)/1000000000),((6643701783:ℚ)/7625000000),((257580869:ℚ)/269000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1572800117:ℚ)/5000000000),((-109086310292123522902388789235191320624783901643351117:ℚ)/2770764160156250000000000000000000000000000000000000000),((-5744608715558514714241497:ℚ)/29573120000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((728647083:ℚ)/1000000000),((7402813233:ℚ)/10000000000),((5356529581:ℚ)/6147500000),((23360439699:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((720595649:ℚ)/2500000000),((-3571996446770533754242522730183773199278640481327879:ℚ)/90751883416748046875000000000000000000000000000000000),((-573500931801111267390253017:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7345853783:ℚ)/10000000000),((7462200211:ℚ)/10000000000),((17993658827:ℚ)/20650000000),((23538600633:ℚ)/24590000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((648347393:ℚ)/2500000000),((-6313830816660817352323714476909748066119811998989839:ℚ)/160452343750000000000000000000000000000000000000000000),((-572540539040238231767050913:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3702618307:ℚ)/5000000000),((3790486811:ℚ)/5000000000),((27198328149:ℚ)/31450000000),((3982486811:ℚ)/4130000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2268786933:ℚ)/10000000000),((-7309213596776822863046700277585124271389814878241999:ℚ)/189863730621337890625000000000000000000000000000000000),((-142654598588807490375386513:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((7524001921:ℚ)/10000000000),((3909259193:ℚ)/5000000000),((55228013447:ℚ)/64800000000),((12303777579:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((707688409:ℚ)/5000000000),((-2324176803682947193927246815426475273371030715400968879:ℚ)/62985600000000000000000000000000000000000000000000000000),((-197475871:ℚ)/1024000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((776153119:ℚ)/1000000000),((971879993:ℚ)/1000000000),((5689071833:ℚ)/8000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-12714922901150112491532473115022954024357648774901441:ℚ)/600000000000000000000000000000000000000000000000000000),((-197475871:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((9661715279:ℚ)/10000000000),((1351913041:ℚ)/1000000000),((23397335651:ℚ)/36800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-161378900711967564459647033285475723:ℚ)/12459008000000000000000000000000000000),((-197475871:ℚ)/1024000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2383:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((2459:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC31
#check @N11Formalization.C450TenthGroupedC31.bound
#print axioms N11Formalization.C450TenthGroupedC31.valid0
#print axioms N11Formalization.C450TenthGroupedC31.valid1
#print axioms N11Formalization.C450TenthGroupedC31.valid2
#print axioms N11Formalization.C450TenthGroupedC31.valid3
#print axioms N11Formalization.C450TenthGroupedC31.valid4
#print axioms N11Formalization.C450TenthGroupedC31.valid5
#print axioms N11Formalization.C450TenthGroupedC31.valid6
#print axioms N11Formalization.C450TenthGroupedC31.valid7
#print axioms N11Formalization.C450TenthGroupedC31.valid8
#print axioms N11Formalization.C450TenthGroupedC31.valid9
#print axioms N11Formalization.C450TenthGroupedC31.valid10
#print axioms N11Formalization.C450TenthGroupedC31.valid11
#print axioms N11Formalization.C450TenthGroupedC31.valid12
#print axioms N11Formalization.C450TenthGroupedC31.valid13
#print axioms N11Formalization.C450TenthGroupedC31.valid14
#print axioms N11Formalization.C450TenthGroupedC31.valid15
#print axioms N11Formalization.C450TenthGroupedC31.valid16
#print axioms N11Formalization.C450TenthGroupedC31.bound
#print axioms N11Formalization.C450TenthGroupedC31.endpoint_checks
