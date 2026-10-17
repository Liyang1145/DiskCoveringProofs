import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2869943501:ℚ)/5000000000),((1255826451:ℚ)/2000000000),((41149265513:ℚ)/53400000000),((9622785157:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1786908689:ℚ)/2500000000),((-49149066122435707679802124966090920613:ℚ)/951708150000000000000000000000000000000),((-432181942355755205783951:ℚ)/1638400000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6215251117:ℚ)/10000000000),((1629208507:ℚ)/2500000000),((88478264521:ℚ)/110600000000),((4148153183:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((613225107:ℚ)/1000000000),((-1493603821795295984444287246328671532236359006502394927413:ℚ)/25366856550000000000000000000000000000000000000000000000000),((-242073883596133396725867639:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((645291439:ℚ)/1000000000),((337726119:ℚ)/500000000),((832435337:ℚ)/1040000000),((2572082833:ℚ)/2765000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5565783467:ℚ)/10000000000),((-414851851178736442974875449266362865676792920432927:ℚ)/7030400000000000000000000000000000000000000000000000),((-9614791639319501746464671:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1338113361:ℚ)/2000000000),((1374672387:ℚ)/2000000000),((18931473693:ℚ)/23260000000),((10454706709:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2471112959:ℚ)/5000000000),((-1224636969829328815942074753529049840828778705807145707:ℚ)/19662971837500000000000000000000000000000000000000000000),((-153291270873824181775831559:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3404694637:ℚ)/5000000000),((437012413:ℚ)/625000000),((48101030281:ℚ)/59100000000),((3319086891:ℚ)/3634375000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((920361349:ℚ)/2000000000),((-60253131572223187346676898942367538475994223820415679637:ℚ)/967617520312500000000000000000000000000000000000000000000),((-14916583737104039866804359:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6928209411:ℚ)/10000000000),((7051615907:ℚ)/10000000000),((97746722343:ℚ)/119150000000),((53521311349:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4236208919:ℚ)/10000000000),((-674887833476175111538560742760774779616358375656552026737:ℚ)/10572121786718750000000000000000000000000000000000000000000),((-3811826719977849286209607239:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6987618641:ℚ)/10000000000),((888879067:ℚ)/1250000000),((98519042333:ℚ)/120100000000),((6742153469:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2020921337:ℚ)/5000000000),((-43182918562663441091982609086930114333857561141542203107:ℚ)/676688906640625000000000000000000000000000000000000000000),((-59453244292076577578839479:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((55054901:ℚ)/78125000),((717044851:ℚ)/1000000000),((775713713:ℚ)/945703125),((5435313957:ℚ)/6005000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3838213601:ℚ)/10000000000),((-149879540555788000173095597136183715037574284029447:ℚ)/2349427087604999542236328125000000000000000000000000),((-37981881791371803751851111:ℚ)/147865600000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((3553217743:ℚ)/5000000000),((3614931923:ℚ)/5000000000),((50031830659:ℚ)/61000000000),((3042724829:ℚ)/3362500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3623756571:ℚ)/10000000000),((-90471379216840048589052955137195250018843974641132205709:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-947842087843514151811937319:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7165843127:ℚ)/10000000000),((3644639279:ℚ)/5000000000),((100835960651:ℚ)/122950000000),((27592474953:ℚ)/30500000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((424552117:ℚ)/1250000000),((-185145171010138340481304346001151287532708351913379172941:ℚ)/2904060269335937500000000000000000000000000000000000000000),((-946137037452692345652071151:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((7225250263:ℚ)/10000000000),((7348692661:ℚ)/10000000000),((101608253419:ℚ)/123900000000),((55600848627:ℚ)/61475000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((630681047:ℚ)/2000000000),((-252550480714271861019818133822168149824830155858398665983:ℚ)/3962531081250000000000000000000000000000000000000000000000),((-3777727572739337428023755031:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3642328453:ℚ)/5000000000),((7467519093:ℚ)/10000000000),((51190269889:ℚ)/62900000000),((56432633651:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2890766971:ℚ)/10000000000),((-94521656470653756506596176970868698836251659795636591:ℚ)/1518909844970703125000000000000000000000000000000000000),((-3764085286041576618773817239:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7403468757:ℚ)/10000000000),((3852582613:ℚ)/5000000000),((11547232649:ℚ)/14400000000),((29048078291:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1139552551:ℚ)/5000000000),((-1520989394331510837407087836309407676770459272912439:ℚ)/25600000000000000000000000000000000000000000000000000),((-259617261:ℚ)/1024000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((1528217403:ℚ)/2000000000),((2401521059:ℚ)/2500000000),((21402826239:ℚ)/32000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-406270677432298348060996574998408211940430463754069321:ℚ)/12800000000000000000000000000000000000000000000000000000),((-259617261:ℚ)/1024000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1908366149:ℚ)/2000000000),((6703581377:ℚ)/5000000000),((26344759937:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-349513026938327179804967671564188541:ℚ)/21529165824000000000000000000000000000),((-259617261:ℚ)/1024000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
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
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source14 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC30
#check @N11Formalization.C450Source14GroupedC30.bound
#print axioms N11Formalization.C450Source14GroupedC30.valid0
#print axioms N11Formalization.C450Source14GroupedC30.valid1
#print axioms N11Formalization.C450Source14GroupedC30.valid2
#print axioms N11Formalization.C450Source14GroupedC30.valid3
#print axioms N11Formalization.C450Source14GroupedC30.valid4
#print axioms N11Formalization.C450Source14GroupedC30.valid5
#print axioms N11Formalization.C450Source14GroupedC30.valid6
#print axioms N11Formalization.C450Source14GroupedC30.valid7
#print axioms N11Formalization.C450Source14GroupedC30.valid8
#print axioms N11Formalization.C450Source14GroupedC30.valid9
#print axioms N11Formalization.C450Source14GroupedC30.valid10
#print axioms N11Formalization.C450Source14GroupedC30.valid11
#print axioms N11Formalization.C450Source14GroupedC30.valid12
#print axioms N11Formalization.C450Source14GroupedC30.valid13
#print axioms N11Formalization.C450Source14GroupedC30.valid14
#print axioms N11Formalization.C450Source14GroupedC30.bound
#print axioms N11Formalization.C450Source14GroupedC30.endpoint_checks
