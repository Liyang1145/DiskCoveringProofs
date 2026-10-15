import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5986231671:ℚ)/10000000000),((162735219:ℚ)/250000000),((2507410557:ℚ)/7120000000),((592205657:ℚ)/1240000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((8297391:ℚ)/12500000),((69417942658976987928350384674604459:ℚ)/3775592176000000000000000000000000000),((-210354429874218244076793:ℚ)/1155200000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1615642719:ℚ)/2500000000),((1349489127:ℚ)/2000000000),((1999642719:ℚ)/5530000000),((4880467381:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1385421377:ℚ)/2500000000),((108857864897940224874877924118260681303325958619405392969623:ℚ)/6984982023440400000000000000000000000000000000000000000000000),((-13826502266431936023301377:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3350335597:ℚ)/5000000000),((6866450427:ℚ)/10000000000),((4118335597:ℚ)/11250000000),((3537050183:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((982824819:ℚ)/2000000000),((1195659992480252104839241596339983713722226869308098709:ℚ)/83200331250000000000000000000000000000000000000000000000),((-350207912329700112716743977:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((681970609:ℚ)/1000000000),((698544673:ℚ)/1000000000),((835570609:ℚ)/2288000000),((2511634019:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((228557283:ℚ)/500000000),((322888404649764712330126186326515051507894333546402522051:ℚ)/22746766662597656250000000000000000000000000000000000000000),((-3524596019773613416653777:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((693873149:ℚ)/1000000000),((7104434961:ℚ)/10000000000),((847473149:ℚ)/2326000000),((1959484991:ℚ)/4400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((210120081:ℚ)/500000000),((7581088328189322422750202950126990007057483604316616633253:ℚ)/540080801700000000000000000000000000000000000000000000000000),((-354710412440112786961361073:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/16),((3:ℚ)/8),((352887393:ℚ)/500000000),((1790981543:ℚ)/2500000000),((429687393:ℚ)/1172500000),((6412944629:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1900183339:ℚ)/5000000000),((42836672377064815004198296534695641523586821627761014570447:ℚ)/3167788292247317504882812500000000000000000000000000000000000),((-22311342633534305243620737:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3558626399:ℚ)/5000000000),((722341551:ℚ)/1000000000),((4326626399:ℚ)/11820000000),((2583024653:ℚ)/5862500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3583390817:ℚ)/10000000000),((7364732643644040442316981964390689531734747231915926997:ℚ)/547075791714477539062500000000000000000000000000000000000),((-3581063026949150587768113:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/16),((3:ℚ)/8),((179418891:ℚ)/250000000),((364145151:ℚ)/500000000),((217818891:ℚ)/595750000),((1300435453:ℚ)/2955000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((838262793:ℚ)/2500000000),((36829605205208581737548177801238728953192059909192735065831:ℚ)/2747399484402935156250000000000000000000000000000000000000000),((-898077272030086642381713:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7236256437:ℚ)/10000000000),((1468477749:ℚ)/2000000000),((8772256437:ℚ)/24020000000),((5237433247:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3106371621:ℚ)/10000000000),((12725749397523317707408982197615753993793873140374219527047:ℚ)/953077439830306982421875000000000000000000000000000000000000),((-14414212058823511450466313:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((7295755237:ℚ)/10000000000),((7461355007:ℚ)/10000000000),((8831755237:ℚ)/24400000000),((26544065021:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((283909107:ℚ)/1000000000),((68799441812106451756644566733655827301660790319897534278949:ℚ)/5035918843219531250000000000000000000000000000000000000000000),((-361457655851380619431400337:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7414747037:ℚ)/10000000000),((3849633941:ℚ)/5000000000),((8950747037:ℚ)/25160000000),((13628901823:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((55311691:ℚ)/250000000),((14701896720969159651632646184477754460864739855550847786519:ℚ)/1031743908789062500000000000000000000000000000000000000000000),((-11963738710722093:ℚ)/60800000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((382635433:ℚ)/500000000),((7937156487:ℚ)/10000000000),((459435433:ℚ)/1296000000),((27971469461:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((47881722924825865929039024990638003593406204868569674778407:ℚ)/3401580370893750000000000000000000000000000000000000000000000),((-25433883:ℚ)/128000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((3945321569:ℚ)/5000000000),((4919799797:ℚ)/5000000000),((4713321569:ℚ)/16000000000),((16839399391:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1245113112934301626925328980706779:ℚ)/60000000000000000000000000000000000),((-25433883:ℚ)/128000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((979337449:ℚ)/1000000000),((13642465337:ℚ)/10000000000),((1132937449:ℚ)/4416000000),((45087396011:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5929584921092942546801:ℚ)/203136000000000000000000),((-25433883:ℚ)/128000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC22
#check @N11Formalization.C450Source14GroupedC22.bound
#print axioms N11Formalization.C450Source14GroupedC22.valid0
#print axioms N11Formalization.C450Source14GroupedC22.valid1
#print axioms N11Formalization.C450Source14GroupedC22.valid2
#print axioms N11Formalization.C450Source14GroupedC22.valid3
#print axioms N11Formalization.C450Source14GroupedC22.valid4
#print axioms N11Formalization.C450Source14GroupedC22.valid5
#print axioms N11Formalization.C450Source14GroupedC22.valid6
#print axioms N11Formalization.C450Source14GroupedC22.valid7
#print axioms N11Formalization.C450Source14GroupedC22.valid8
#print axioms N11Formalization.C450Source14GroupedC22.valid9
#print axioms N11Formalization.C450Source14GroupedC22.valid10
#print axioms N11Formalization.C450Source14GroupedC22.valid11
#print axioms N11Formalization.C450Source14GroupedC22.valid12
#print axioms N11Formalization.C450Source14GroupedC22.valid13
#print axioms N11Formalization.C450Source14GroupedC22.bound
#print axioms N11Formalization.C450Source14GroupedC22.endpoint_checks
