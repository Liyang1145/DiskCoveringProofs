import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((122592239:ℚ)/200000000),((1327610221:ℚ)/2000000000),((250592239:ℚ)/2136000000),((2031610221:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6325409941:ℚ)/10000000000),((9643363444591665017121984388928490293:ℚ)/362456848896000000000000000000000000000),((-96386849381673680490177:ℚ)/1182924800000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6605709419:ℚ)/10000000000),((1375192469:ℚ)/2000000000),((13005709419:ℚ)/110600000000),((2079192469:ℚ)/10680000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5172702731:ℚ)/10000000000),((175632180796134199583383483682317410689701105640688819793:ℚ)/6929545658175000000000000000000000000000000000000000000000),((-255088940319272085746522457:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((1368740283:ℚ)/2000000000),((6994907521:ℚ)/10000000000),((2648740283:ℚ)/22500000000),((10514907521:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((899816401:ℚ)/2000000000),((6329139778237627156221454335221898368442797243963983837:ℚ)/254801014453125000000000000000000000000000000000000000000),((-31458066841882248891876779:ℚ)/354877440000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((435167807:ℚ)/625000000),((7054377651:ℚ)/10000000000),((835167807:ℚ)/7090625000),((10574377651:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2062234121:ℚ)/5000000000),((978866082998831257885556858967446378733590080429075212618923:ℚ)/39769863224029541015625000000000000000000000000000000000000000),((-1037818719002202295796513:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((7022173719:ℚ)/10000000000),((3556923099:ℚ)/5000000000),((13422173719:ℚ)/114400000000),((5316923099:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3924620201:ℚ)/10000000000),((715802165606798343239133567194412342448329127992179494813:ℚ)/29159872381340454101562500000000000000000000000000000000000),((-802341515043750774955754771:ℚ)/8871936000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((7081660631:ℚ)/10000000000),((17933283:ℚ)/25000000),((4493886877:ℚ)/38450000000),((26733283:ℚ)/143000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1857312979:ℚ)/5000000000),((4134846462661734856819810372624172403362713444099331:ℚ)/168873239817089843750000000000000000000000000000000000),((-269212794638629135904964657:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3570572847:ℚ)/5000000000),((904097337:ℚ)/1250000000),((6770572847:ℚ)/58150000000),((1344097337:ℚ)/7209375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1746325813:ℚ)/5000000000),((1790977224619029259016426238566525555463941791368788917:ℚ)/73324405178847432136535644531250000000000000000000000000),((-203233846719464235074799299:ℚ)/2217984000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((1440125791:ℚ)/2000000000),((3646121361:ℚ)/5000000000),((2720125791:ℚ)/23450000000),((5406121361:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((814060899:ℚ)/2500000000),((27432614460559056646256988824150035682230405543901464653:ℚ)/1125724339817810058593750000000000000000000000000000000000),((-10909767041165267988956897:ℚ)/118292480000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((907513807:ℚ)/1250000000),((3675852657:ℚ)/5000000000),((569171269:ℚ)/4925000000),((5435852657:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((23453039:ℚ)/78125000),((2320969378648988549949359327769496495706101022340734173849:ℚ)/95453328241848945617675781250000000000000000000000000000000),((-4289217766968133765024513:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((45747439:ℚ)/62500000),((7470626331:ℚ)/10000000000),((85747439:ℚ)/750625000),((10990626331:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2724891423:ℚ)/10000000000),((943675582368607101601781081853987739832749979390452106256241:ℚ)/38769235525451953125000000000000000000000000000000000000000000),((-10792021356674558557377:ℚ)/115520000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((929818103:ℚ)/1250000000),((7589542011:ℚ)/10000000000),((1729818103:ℚ)/15250000000),((11109542011:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1032466703:ℚ)/5000000000),((7631163629014476697882508578642621885742185105580445586843:ℚ)/314744927701220703125000000000000000000000000000000000000000),((-4371992448577458432334833:ℚ)/46208000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7557493019:ℚ)/10000000000),((4032578029:ℚ)/5000000000),((4652497673:ℚ)/43200000000),((5792578029:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((529067353:ℚ)/5000000000),((271290473117749315198112036501954144443006312331982371:ℚ)/11037634277343750000000000000000000000000000000000000000),((-283339495160972138693704057:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((4016613777:ℚ)/5000000000),((398681123:ℚ)/400000000),((7216613777:ℚ)/80000000000),((59942347:ℚ)/288000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4977992657724949546211091332322696962743663777:ℚ)/194400000000000000000000000000000000000000000000),((-98546319:ℚ)/1024000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((9935466703:ℚ)/10000000000),((13769224337:ℚ)/10000000000),((16335466703:ℚ)/220800000000),((17289224337:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((124760056427776930296694677291996872987:ℚ)/4232000000000000000000000000000000000000),((-98546319:ℚ)/1024000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC18
#check @N11Formalization.C450Source12GroupedC18.bound
#print axioms N11Formalization.C450Source12GroupedC18.valid0
#print axioms N11Formalization.C450Source12GroupedC18.valid1
#print axioms N11Formalization.C450Source12GroupedC18.valid2
#print axioms N11Formalization.C450Source12GroupedC18.valid3
#print axioms N11Formalization.C450Source12GroupedC18.valid4
#print axioms N11Formalization.C450Source12GroupedC18.valid5
#print axioms N11Formalization.C450Source12GroupedC18.valid6
#print axioms N11Formalization.C450Source12GroupedC18.valid7
#print axioms N11Formalization.C450Source12GroupedC18.valid8
#print axioms N11Formalization.C450Source12GroupedC18.valid9
#print axioms N11Formalization.C450Source12GroupedC18.valid10
#print axioms N11Formalization.C450Source12GroupedC18.valid11
#print axioms N11Formalization.C450Source12GroupedC18.valid12
#print axioms N11Formalization.C450Source12GroupedC18.valid13
#print axioms N11Formalization.C450Source12GroupedC18.bound
#print axioms N11Formalization.C450Source12GroupedC18.endpoint_checks
