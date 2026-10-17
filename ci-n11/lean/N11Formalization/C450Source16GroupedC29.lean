import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5702625703:ℚ)/10000000000),((249788597:ℚ)/400000000),((19347877109:ℚ)/26700000000),((3631251761:ℚ)/3968000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7222117657:ℚ)/10000000000),((-2993387539473234886395887908782574381:ℚ)/59481759375000000000000000000000000000),((-5745118360361190694379:ℚ)/19456000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1544582343:ℚ)/2500000000),((3241284409:ℚ)/5000000000),((5193747029:ℚ)/6912500000),((46936697317:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1554041573:ℚ)/2500000000),((-4534050390046777772655106427751132618777809573910041:ℚ)/77413502655029296875000000000000000000000000000000000),((-892663772356891441611011:ℚ)/3040000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1604036217:ℚ)/2500000000),((6720399151:ℚ)/10000000000),((413239127:ℚ)/550000000),((96965188963:ℚ)/110600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1414175441:ℚ)/2500000000),((-763883461685450652434004760425612039980249385121:ℚ)/12998046875000000000000000000000000000000000000000),((-3550537503624232730084131:ℚ)/12160000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3326969683:ℚ)/5000000000),((3419653103:ℚ)/5000000000),((11100909049:ℚ)/14537500000),((4477771849:ℚ)/5200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1260721997:ℚ)/2500000000),((-11243756414064632614528963327249163271940029812893621:ℚ)/180019883766174316406250000000000000000000000000000000),((-885112754704929407110579:ℚ)/3040000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1354565877:ℚ)/2000000000),((6958208203:ℚ)/10000000000),((4511697631:ℚ)/5910000000),((100056706639:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2354484223:ℚ)/5000000000),((-755454251842254215878756640480902596989514497065891:ℚ)/12095219003906250000000000000000000000000000000000000),((-3530346046443574586219179:ℚ)/12160000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1378342979:ℚ)/2000000000),((350882869:ℚ)/500000000),((4583028937:ℚ)/5957500000),((5041477297:ℚ)/5910000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4351552881:ℚ)/10000000000),((-3182345520516806278868820018953189874273259683125917:ℚ)/49556820875244140625000000000000000000000000000000000),((-8813216554408471118291:ℚ)/30400000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3475578013:ℚ)/5000000000),((7077105381:ℚ)/10000000000),((11546734039:ℚ)/15012500000),((101602369953:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((4162149421:ℚ)/10000000000),((-1060558929630298164547817567337739506524392235094737:ℚ)/16520725259780883789062500000000000000000000000000000),((-3520222568541227807697291:ℚ)/12160000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((701059611:ℚ)/1000000000),((1427310447:ℚ)/2000000000),((2327178833:ℚ)/3026250000),((20475035811:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1982130429:ℚ)/5000000000),((-15439312114829563100537552711853172564278714471679:ℚ)/240581333770751953125000000000000000000000000000000),((-140606155383356075167779:ℚ)/486400000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((707003517:ℚ)/1000000000),((7195997967:ℚ)/10000000000),((2345010551:ℚ)/3050000000),((34382657857:ℚ)/40350000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3756542597:ℚ)/10000000000),((-142204853593384599814785452058285829791793205172353:ℚ)/2216611328125000000000000000000000000000000000000000),((-3510080568030521606463459:ℚ)/12160000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((445592077:ℚ)/625000000),((1828721543:ℚ)/2500000000),((210968033:ℚ)/276562500),((26173380059:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3537259273:ℚ)/10000000000),((-955510219344358299569549730177341233046940753:ℚ)/15301927924156188964843750000000000000000000000),((-218745001815840612607019:ℚ)/760000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((453021653:ℚ)/625000000),((1858442549:ℚ)/2500000000),((1499064959:ℚ)/1965625000),((26559753137:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3053899001:ℚ)/10000000000),((-1063976063532714771690919258939521673726115987:ℚ)/17041709506884217262268066406250000000000000000),((-218108808535024175583731:ℚ)/760000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((3683607969:ℚ)/5000000000),((1534305287:ℚ)/2000000000),((12170823907:ℚ)/16200000000),((21865968731:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2481416233:ℚ)/10000000000),((-729382717516502693288130085631612339736957573130103:ℚ)/12301875000000000000000000000000000000000000000000000),((-36583961:ℚ)/128000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((760494439:ℚ)/1000000000),((598321103:ℚ)/625000000),((2505483317:ℚ)/4000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-26584862222968169284014275730769765746765200838593:ℚ)/937500000000000000000000000000000000000000000000000),((-36583961:ℚ)/128000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4753190469:ℚ)/5000000000),((3343757023:ℚ)/2500000000),((15379571407:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-637363363557371388891978452507603:ℚ)/65701800000000000000000000000000000),((-36583961:ℚ)/128000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC29
#check @N11Formalization.C450Source16GroupedC29.bound
#print axioms N11Formalization.C450Source16GroupedC29.valid0
#print axioms N11Formalization.C450Source16GroupedC29.valid1
#print axioms N11Formalization.C450Source16GroupedC29.valid2
#print axioms N11Formalization.C450Source16GroupedC29.valid3
#print axioms N11Formalization.C450Source16GroupedC29.valid4
#print axioms N11Formalization.C450Source16GroupedC29.valid5
#print axioms N11Formalization.C450Source16GroupedC29.valid6
#print axioms N11Formalization.C450Source16GroupedC29.valid7
#print axioms N11Formalization.C450Source16GroupedC29.valid8
#print axioms N11Formalization.C450Source16GroupedC29.valid9
#print axioms N11Formalization.C450Source16GroupedC29.valid10
#print axioms N11Formalization.C450Source16GroupedC29.valid11
#print axioms N11Formalization.C450Source16GroupedC29.valid12
#print axioms N11Formalization.C450Source16GroupedC29.valid13
#print axioms N11Formalization.C450Source16GroupedC29.bound
#print axioms N11Formalization.C450Source16GroupedC29.endpoint_checks
