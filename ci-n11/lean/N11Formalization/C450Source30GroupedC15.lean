import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((6163448713:ℚ)/10000000000),((810108493:ℚ)/1250000000),((309891507:ℚ)/6437500000),((12396551287:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3124854943:ℚ)/5000000000),((16271104131013019738054124415795996971974857004851407:ℚ)/1667369079589843750000000000000000000000000000000000000),((-538532139259785478761977877:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((640503997:ℚ)/1000000000),((6601394129:ℚ)/10000000000),((2358605871:ℚ)/52450000000),((1215496003:ℚ)/10300000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1136781019:ℚ)/2000000000),((2511417162891538457346518852570473836888917102175064971:ℚ)/225453251757812500000000000000000000000000000000000000000),((-5736901965180673646237997:ℚ)/29573120000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3262860849:ℚ)/5000000000),((26257249:ℚ)/39062500),((8742751:ℚ)/208593750),((6017139151:ℚ)/52450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((269085509:ℚ)/500000000),((10013516320977928251319077811111548956497223833:ℚ)/787864252924919128417968750000000000000000000000),((-443487688150811233115409199:ℚ)/2217984000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6646333069:ℚ)/10000000000),((6842256269:ℚ)/10000000000),((2117743731:ℚ)/54350000000),((11913666931:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5063562437:ℚ)/10000000000),((14265721745425919379197329793465657186696716110055842279:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-608976143184540064764350413:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3383438943:ℚ)/5000000000),((6962598939:ℚ)/10000000000),((1997401061:ℚ)/55300000000),((5896561057:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1181549991:ℚ)/2500000000),((258732040091090404577979106399009568826842774797158041:ℚ)/16514880566406250000000000000000000000000000000000000000),((-470001268094042517099132751:ℚ)/2217984000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6887359681:ℚ)/10000000000),((7082886763:ℚ)/10000000000),((1877113237:ℚ)/56250000000),((11672640319:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2182563507:ℚ)/5000000000),((915275059066679904104255597298827491919493014454857:ℚ)/53644180297851562500000000000000000000000000000000000),((-644394009860652051420529413:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7007781737:ℚ)/10000000000),((7203122541:ℚ)/10000000000),((1756877459:ℚ)/57200000000),((1283579807:ℚ)/12500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3973840397:ℚ)/10000000000),((21530485301276439265938990904859184930512244222004373951:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-662153518168856805668184277:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1425629423:ℚ)/2000000000),((3721724123:ℚ)/5000000000),((758275877:ℚ)/29550000000),((2286370577:ℚ)/22880000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1771146561:ℚ)/5000000000),((94527249903442440560231379114668793972772861738539593:ℚ)/4479710742187500000000000000000000000000000000000000000),((-27197890879439781703192357:ℚ)/118292480000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7368719053:ℚ)/10000000000),((960449371:ℚ)/1250000000),((159550629:ℚ)/7625000000),((11191280947:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((618337657:ℚ)/2500000000),((65026857744086772460449594641763389647812917819452881:ℚ)/2770764160156250000000000000000000000000000000000000000),((-715638943484399394320824397:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((7609096129:ℚ)/10000000000),((4081707867:ℚ)/5000000000),((398292133:ℚ)/32400000000),((10950903871:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8160777514379877910517708858562669061972321223471417:ℚ)/291600000000000000000000000000000000000000000000000000),((-259734283:ℚ)/1024000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((4044667899:ℚ)/5000000000),((2519637619:ℚ)/2500000000),((-279637619:ℚ)/16200000000),((5235332101:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2683459677470283362302378850949466775326737918495187:ℚ)/61509375000000000000000000000000000000000000000000000),((-259734283:ℚ)/1024000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10005256727:ℚ)/10000000000),((13896924413:ℚ)/10000000000),((-4936924413:ℚ)/80000000000),((8554743273:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((9141983645358719688762596811803297061:ℚ)/128000000000000000000000000000000000000),((-259734283:ℚ)/1024000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC15
#check @N11Formalization.C450Source30GroupedC15.bound
#print axioms N11Formalization.C450Source30GroupedC15.valid0
#print axioms N11Formalization.C450Source30GroupedC15.valid1
#print axioms N11Formalization.C450Source30GroupedC15.valid2
#print axioms N11Formalization.C450Source30GroupedC15.valid3
#print axioms N11Formalization.C450Source30GroupedC15.valid4
#print axioms N11Formalization.C450Source30GroupedC15.valid5
#print axioms N11Formalization.C450Source30GroupedC15.valid6
#print axioms N11Formalization.C450Source30GroupedC15.valid7
#print axioms N11Formalization.C450Source30GroupedC15.valid8
#print axioms N11Formalization.C450Source30GroupedC15.valid9
#print axioms N11Formalization.C450Source30GroupedC15.valid10
#print axioms N11Formalization.C450Source30GroupedC15.valid11
#print axioms N11Formalization.C450Source30GroupedC15.bound
#print axioms N11Formalization.C450Source30GroupedC15.endpoint_checks
