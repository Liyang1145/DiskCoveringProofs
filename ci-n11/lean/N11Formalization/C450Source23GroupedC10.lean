import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((6465904403:ℚ)/10000000000),((6773679933:ℚ)/10000000000),((-33975759531:ℚ)/99200000000),((-12357713209:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5533344813:ℚ)/10000000000),((1280270529910273421203809953076888303381683415068355957407:ℚ)/6616120507812500000000000000000000000000000000000000000000),((12269737234084639942496013:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1676307339:ℚ)/2500000000),((3446660379:ℚ)/5000000000),((-17406622653:ℚ)/51500000000),((-3268922017:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2450699383:ℚ)/5000000000),((17128050968605917963466478752729094358701507960013794103:ℚ)/90709706761932373046875000000000000000000000000000000000),((624311318709622729410797:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((1364968341:ℚ)/2000000000),((7012929543:ℚ)/10000000000),((-35650506801:ℚ)/104900000000),((-2686905023:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((22779057:ℚ)/50000000),((31354701729629532166627600131236467448231874109835461013:ℚ)/166390308225000000000000000000000000000000000000000000000),((979424628467024053397:ℚ)/25600000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((6944423049:ℚ)/10000000000),((3536361229:ℚ)/5000000000),((-18034528603:ℚ)/53400000000),((-13793269147:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((418400771:ℚ)/1000000000),((47480565183809993173256453588820134833610314011935128153:ℚ)/254831535780429840087890625000000000000000000000000000000),((7683420157907715952507157:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3502101307:ℚ)/5000000000),((891563499:ℚ)/1250000000),((-4560944493:ℚ)/13468750000),((-6986303921:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1992995747:ℚ)/5000000000),((2516119302715051046277346141807946012257859870482115982303:ℚ)/13514685834790039062500000000000000000000000000000000000000),((1775785786886197807372893:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1412795007:ℚ)/2000000000),((7192286339:ℚ)/10000000000),((-36906004373:ℚ)/108700000000),((-2830385021:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((377821723:ℚ)/1000000000),((680653988608811848985856289652511196426839415090421987:ℚ)/3658676880029296875000000000000000000000000000000000000),((260852350673642788255493:ℚ)/9241600000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7123740503:ℚ)/10000000000),((906507211:ℚ)/1250000000),((-4665550477:ℚ)/13706250000),((-14331221509:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3558971333:ℚ)/10000000000),((1683245500638584662058589382410676560006473697996933819269:ℚ)/9054283270532226562500000000000000000000000000000000000000),((5937915732016423940352213:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7183499197:ℚ)/10000000000),((7311822219:ℚ)/10000000000),((-5391822219:ℚ)/15800000000),((-14510497591:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((133039231:ℚ)/400000000),((248681682129774150784228023378296156755135651792641668073:ℚ)/1338584745619201660156250000000000000000000000000000000000),((5352962856060966031744813:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7243251293:ℚ)/10000000000),((7371580107:ℚ)/10000000000),((-38161060749:ℚ)/111550000000),((-14689753879:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3076118457:ℚ)/10000000000),((449948386922420169250240135460998604239466922555711970057:ℚ)/2423523366451263427734375000000000000000000000000000000000),((4766448961908759476778093:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((7302996961:ℚ)/10000000000),((7491076627:ℚ)/10000000000),((-38997536389:ℚ)/112500000000),((-14868990883:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2804873123:ℚ)/10000000000),((44786868673937080560510585138156899489467690233854607649:ℚ)/239253300000000000000000000000000000000000000000000000000),((4178372912421061235292997:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((371123483:ℚ)/500000000),((241562407:ℚ)/312500000),((-97764373:ℚ)/275000000),((-761370449:ℚ)/2955000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((135354767:ℚ)/625000000),((780714497856741427595135855855551168235687683177361:ℚ)/4106401513671875000000000000000000000000000000000000),((7493825082949458668173:ℚ)/577600000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((478834047:ℚ)/625000000),((7968828191:ℚ)/10000000000),((-42341797337:ℚ)/118200000000),((-996502141:ℚ)/3812500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((9699814383136425293883794009122936197331592092630446683:ℚ)/51172550582885742187500000000000000000000000000000000000),((340957:ℚ)/64000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7900133483:ℚ)/10000000000),((8446254557:ℚ)/10000000000),((-45683781899:ℚ)/122000000000),((-16660400449:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((561199255267141156429798812756560887812876364802724666533:ℚ)/2881591200000000000000000000000000000000000000000000000000),((340957:ℚ)/64000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((2094370639:ℚ)/2500000000),((10353642087:ℚ)/10000000000),((-6559499401:ℚ)/14400000000),((-4523111917:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((25021187979824939688392728721595310836670696667891256421:ℚ)/112500000000000000000000000000000000000000000000000000000),((340957:ℚ)/64000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((5142317573:ℚ)/5000000000),((7081146911:ℚ)/5000000000),((-42848028377:ℚ)/80000000000),((-11906952719:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((16729849629924061432021842834468027446183228931712837327:ℚ)/65701800000000000000000000000000000000000000000000000000),((340957:ℚ)/64000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC10
#check @N11Formalization.C450Source23GroupedC10.bound
#print axioms N11Formalization.C450Source23GroupedC10.valid0
#print axioms N11Formalization.C450Source23GroupedC10.valid1
#print axioms N11Formalization.C450Source23GroupedC10.valid2
#print axioms N11Formalization.C450Source23GroupedC10.valid3
#print axioms N11Formalization.C450Source23GroupedC10.valid4
#print axioms N11Formalization.C450Source23GroupedC10.valid5
#print axioms N11Formalization.C450Source23GroupedC10.valid6
#print axioms N11Formalization.C450Source23GroupedC10.valid7
#print axioms N11Formalization.C450Source23GroupedC10.valid8
#print axioms N11Formalization.C450Source23GroupedC10.valid9
#print axioms N11Formalization.C450Source23GroupedC10.valid10
#print axioms N11Formalization.C450Source23GroupedC10.valid11
#print axioms N11Formalization.C450Source23GroupedC10.valid12
#print axioms N11Formalization.C450Source23GroupedC10.valid13
#print axioms N11Formalization.C450Source23GroupedC10.valid14
#print axioms N11Formalization.C450Source23GroupedC10.bound
#print axioms N11Formalization.C450Source23GroupedC10.endpoint_checks
