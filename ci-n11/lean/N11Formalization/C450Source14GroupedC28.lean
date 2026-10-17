import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5800452323:ℚ)/10000000000),((3167946333:ℚ)/5000000000),((71484975553:ℚ)/106800000000),((10543838999:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7025183303:ℚ)/10000000000),((-9070373184104481032114147690588113469:ℚ)/304546608000000000000000000000000000000),((-933183380093550766706014801:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1569033171:ℚ)/2500000000),((3286852991:ℚ)/5000000000),((19179364881:ℚ)/27650000000),((10900558973:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1497911931:ℚ)/2500000000),((-4677300233540154535357234950341477673787964006907318351:ℚ)/132119044531250000000000000000000000000000000000000000000),((-931463917519413254336665929:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6513937733:ℚ)/10000000000),((1362299689:ℚ)/2000000000),((79333315063:ℚ)/114400000000),((4502899067:ℚ)/5530000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5411884129:ℚ)/10000000000),((-333426311533556343726431342842434607197524999094418962273:ℚ)/9357462400000000000000000000000000000000000000000000000000),((-148758391430387597665849689:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6751722479:ℚ)/10000000000),((866298437:ℚ)/1250000000),((81948947269:ℚ)/116300000000),((2858895311:ℚ)/3575000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((149056871:ℚ)/312500000),((-280926283077992780911246263609359049744047394387092261977:ℚ)/7373614439062500000000000000000000000000000000000000000000),((-58054766621611315576495521:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3435303931:ℚ)/5000000000),((704927207:ℚ)/1000000000),((41628343241:ℚ)/59100000000),((2322781621:ℚ)/2907500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4416974477:ℚ)/10000000000),((-36901127668035622039285233259856828760321531155796646997:ℚ)/967617520312500000000000000000000000000000000000000000000),((-37120458136521513563472441:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3494744443:ℚ)/5000000000),((1421742549:ℚ)/2000000000),((42282188873:ℚ)/59575000000),((4681227647:ℚ)/5910000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4035580669:ℚ)/10000000000),((-155810835011650807044329850897184922777841103002926298941:ℚ)/3964545670019531250000000000000000000000000000000000000000),((-148412579549787962345471809:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1762231957:ℚ)/2500000000),((7168152379:ℚ)/10000000000),((21304551527:ℚ)/30025000000),((23584457137:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3831530149:ℚ)/10000000000),((-415566030266015629518649953386272534158001822882101313:ℚ)/10573264166259765625000000000000000000000000000000000000),((-3708582029711886993801399969:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7108365757:ℚ)/10000000000),((7227590997:ℚ)/10000000000),((85872023327:ℚ)/121050000000),((23762772991:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3616585177:ℚ)/10000000000),((-48414776316065619969358122355417851112951565165193186577:ℚ)/1231776428906250000000000000000000000000000000000000000000),((-3706848435885497603618402881:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((7167802697:ℚ)/10000000000),((7287028623:ℚ)/10000000000),((86525829667:ℚ)/122000000000),((23941085869:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1694334511:ℚ)/5000000000),((-446076413869776665002289059112296702599491849644519635373:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-3705113706624548806285425961:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((722723867:ℚ)/1000000000),((1851475247:ℚ)/2500000000),((8717962537:ℚ)/12390000000),((6074425741:ℚ)/7625000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((786239589:ℚ)/2500000000),((-37856579796489872642441919925776268598176708085578541:ℚ)/990632770312500000000000000000000000000000000000000000),((-231352552464392473509115881:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((229565869:ℚ)/312500000),((1881192413:ℚ)/2500000000),((2765224559:ℚ)/3931250000),((6163577239:ℚ)/7743750000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1296042931:ℚ)/5000000000),((-14176943469737600668941064164121486329181883548481:ℚ)/370827598869800567626953125000000000000000000000000),((-640263750584184386945961:ℚ)/2560000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((3732486671:ℚ)/5000000000),((7762496527:ℚ)/10000000000),((44897353381:ℚ)/64800000000),((25367489581:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1887830783:ℚ)/10000000000),((-2280907159910577018692379547950627225499584382093343777:ℚ)/62985600000000000000000000000000000000000000000000000000),((-255952923:ℚ)/1024000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((3851347117:ℚ)/5000000000),((2415980789:ℚ)/2500000000),((46204818287:ℚ)/80000000000),((7767942367:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-9580122240493851986543644070341235875724881365141709931:ℚ)/600000000000000000000000000000000000000000000000000000000),((-255952923:ℚ)/1024000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9604083247:ℚ)/10000000000),((6732798563:ℚ)/5000000000),((113324915717:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-7803746805049589426300113513729485961:ℚ)/2691145728000000000000000000000000000000),((-255952923:ℚ)/1024000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC28
#check @N11Formalization.C450Source14GroupedC28.bound
#print axioms N11Formalization.C450Source14GroupedC28.valid0
#print axioms N11Formalization.C450Source14GroupedC28.valid1
#print axioms N11Formalization.C450Source14GroupedC28.valid2
#print axioms N11Formalization.C450Source14GroupedC28.valid3
#print axioms N11Formalization.C450Source14GroupedC28.valid4
#print axioms N11Formalization.C450Source14GroupedC28.valid5
#print axioms N11Formalization.C450Source14GroupedC28.valid6
#print axioms N11Formalization.C450Source14GroupedC28.valid7
#print axioms N11Formalization.C450Source14GroupedC28.valid8
#print axioms N11Formalization.C450Source14GroupedC28.valid9
#print axioms N11Formalization.C450Source14GroupedC28.valid10
#print axioms N11Formalization.C450Source14GroupedC28.valid11
#print axioms N11Formalization.C450Source14GroupedC28.valid12
#print axioms N11Formalization.C450Source14GroupedC28.valid13
#print axioms N11Formalization.C450Source14GroupedC28.bound
#print axioms N11Formalization.C450Source14GroupedC28.endpoint_checks
