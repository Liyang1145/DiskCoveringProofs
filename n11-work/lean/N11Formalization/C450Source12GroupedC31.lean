import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((1446402271:ℚ)/2500000000),((3161095211:ℚ)/5000000000),((3641605299:ℚ)/4450000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((176383901:ℚ)/250000000),((-10538808156851295692187751919152323:ℚ)/220302812500000000000000000000000000),((-34611165694808279719938347:ℚ)/147865600000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((2445603:ℚ)/3906250),((6559786993:ℚ)/10000000000),((36738442:ℚ)/43203125),((21087360979:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3013729417:ℚ)/5000000000),((-3389384376859393011249447396214056892792130687:ℚ)/62999269738793373107910156250000000000000000000),((-380405567088685160129963:ℚ)/1638400000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6498304039:ℚ)/10000000000),((849672143:ℚ)/1250000000),((48688128273:ℚ)/57200000000),((2725016429:ℚ)/2765000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5451683461:ℚ)/10000000000),((-3937927390874980528754255891853318999705328655099642751:ℚ)/73105175000000000000000000000000000000000000000000000000),((-2128240054644598224609443:ℚ)/9241600000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3367930193:ℚ)/5000000000),((6916170009:ℚ)/10000000000),((25175511351:ℚ)/29075000000),((22156510027:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4815082859:ℚ)/10000000000),((-135824003907181385374131968756373335401944036546052017:ℚ)/2400265116882324218750000000000000000000000000000000000),((-135647542043103131574829267:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((6854637179:ℚ)/10000000000),((43597287:ℚ)/62500000),((51182460253:ℚ)/58625000000),((139591861:ℚ)/145375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((446588037:ℚ)/1000000000),((-4558557279056806060024303823326484297301083563734014779:ℚ)/78706137847900390625000000000000000000000000000000000000),((-5287795179172975428883:ℚ)/23104000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6914025249:ℚ)/10000000000),((1406992299:ℚ)/2000000000),((51598176743:ℚ)/59100000000),((643225271:ℚ)/670000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1070346341:ℚ)/2500000000),((-129676223093582100034554748077769806053212506277098169:ℚ)/2239855371093750000000000000000000000000000000000000000),((-5403500850291251214910507:ℚ)/23658496000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((697341311:ℚ)/1000000000),((3547178371:ℚ)/5000000000),((5201389177:ℚ)/5957500000),((11345535113:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4089110201:ℚ)/10000000000),((-4779939137912420885662378630220827388221193646116191:ℚ)/82594701458740234375000000000000000000000000000000000),((-33701859004401833143916187:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1406560153:ℚ)/2000000000),((1788437917:ℚ)/2500000000),((10485921071:ℚ)/12010000000),((5717313751:ℚ)/5957500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3887897073:ℚ)/10000000000),((-9786718702617725150166936719067179848767447522043073:ℚ)/169172226660156250000000000000000000000000000000000000),((-8407956302227524333202523:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((354609411:ℚ)/500000000),((3606573141:ℚ)/5000000000),((2642265877:ℚ)/3026250000),((11523719423:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3676274807:ℚ)/10000000000),((-52173140394565688103941709952831473118120655114873:ℚ)/902180001640319824218750000000000000000000000000000),((-92968916668805183288947:ℚ)/409600000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((7151575479:ℚ)/10000000000),((7272540589:ℚ)/10000000000),((53261028353:ℚ)/61000000000),((23225621767:ℚ)/24210000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3452325679:ℚ)/10000000000),((-84028563416952946446567026292665567564826015754400531:ℚ)/1453515625000000000000000000000000000000000000000000000),((-133966880497167857254745147:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((7210962547:ℚ)/10000000000),((7331934599:ℚ)/10000000000),((53676737829:ℚ)/61475000000),((23403803797:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1606734597:ℚ)/5000000000),((-327796182748658985306104920906390365584909451518390283:ℚ)/5671992713546752929687500000000000000000000000000000000),((-133686595271482637406188307:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7270349429:ℚ)/10000000000),((1847832079:ℚ)/2500000000),((54092446003:ℚ)/61950000000),((5895496237:ℚ)/6147500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((1478044649:ℚ)/5000000000),((-596180899318392257793196019935164672839469407234129741:ℚ)/10319091357421875000000000000000000000000000000000000000),((-8337891248411836859876387:ℚ)/36966400000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((7329736129:ℚ)/10000000000),((7510114903:ℚ)/10000000000),((54508152903:ℚ)/62900000000),((23938344709:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1337419569:ℚ)/5000000000),((-1373345283884645160102697798374194933170452486308728209:ℚ)/24302557519531250000000000000000000000000000000000000000),((-132845439019117113925210163:ℚ)/591462400000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((3724254499:ℚ)/5000000000),((7747684857:ℚ)/10000000000),((27669781493:ℚ)/32400000000),((24651054571:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1999980091:ℚ)/10000000000),((-986771657061629135499358604004956633792682860944859:ℚ)/18225000000000000000000000000000000000000000000000000),((-229260617:ℚ)/1024000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((7686052723:ℚ)/10000000000),((9648124827:ℚ)/10000000000),((57002369061:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-386742690027001252395455362015924341569134656820164243:ℚ)/12500000000000000000000000000000000000000000000000000000),((-229260617:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((9586327741:ℚ)/10000000000),((336216031:ℚ)/250000000),((23434764729:ℚ)/36800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-14605630380258172140168037521676461:ℚ)/778688000000000000000000000000000000),((-229260617:ℚ)/1024000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source12 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC31
#check @N11Formalization.C450Source12GroupedC31.bound
#print axioms N11Formalization.C450Source12GroupedC31.valid0
#print axioms N11Formalization.C450Source12GroupedC31.valid1
#print axioms N11Formalization.C450Source12GroupedC31.valid2
#print axioms N11Formalization.C450Source12GroupedC31.valid3
#print axioms N11Formalization.C450Source12GroupedC31.valid4
#print axioms N11Formalization.C450Source12GroupedC31.valid5
#print axioms N11Formalization.C450Source12GroupedC31.valid6
#print axioms N11Formalization.C450Source12GroupedC31.valid7
#print axioms N11Formalization.C450Source12GroupedC31.valid8
#print axioms N11Formalization.C450Source12GroupedC31.valid9
#print axioms N11Formalization.C450Source12GroupedC31.valid10
#print axioms N11Formalization.C450Source12GroupedC31.valid11
#print axioms N11Formalization.C450Source12GroupedC31.valid12
#print axioms N11Formalization.C450Source12GroupedC31.valid13
#print axioms N11Formalization.C450Source12GroupedC31.valid14
#print axioms N11Formalization.C450Source12GroupedC31.valid15
#print axioms N11Formalization.C450Source12GroupedC31.bound
#print axioms N11Formalization.C450Source12GroupedC31.endpoint_checks
