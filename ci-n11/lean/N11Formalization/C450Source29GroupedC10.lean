import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6523629337:ℚ)/10000000000),((1345594511:ℚ)/2000000000),((-5963161577:ℚ)/19840000000),((-10610888011:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1077415797:ℚ)/2000000000),((408942411215659361698628622150374053189919:ℚ)/1995571639812096000000000000000000000000000),((130247472630874323599599307:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((1660982079:ℚ)/2500000000),((342411569:ℚ)/500000000),((-1532880983:ℚ)/5055000000),((-2742946237:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5070082703:ℚ)/10000000000),((109869293444938559017329837881837695336268508332780058067:ℚ)/535300888065380859375000000000000000000000000000000000000),((7321887502650750019360123:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((6764169067:ℚ)/10000000000),((348421727:ℚ)/500000000),((-1574952089:ℚ)/5150000000),((-11332507201:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2367011833:ℚ)/5000000000),((754379100441254136940036627705709269747765952758093560749:ℚ)/3669549205099487304687500000000000000000000000000000000000),((103934824265876459084980067:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((6884354831:ℚ)/10000000000),((3514258103:ℚ)/5000000000),((-15959806721:ℚ)/52450000000),((-11693064493:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4374469413:ℚ)/10000000000),((11289218309140330026692627295291504043716333501692239947772653:ℚ)/55365005940669531250000000000000000000000000000000000000000000),((90601164806712664826557083:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6944428041:ℚ)/10000000000),((3544292539:ℚ)/5000000000),((-16170047773:ℚ)/52925000000),((-11873284123:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4183991543:ℚ)/10000000000),((1123416082644642341365840363076459927026782404072098151368219:ℚ)/5504322787395483398437500000000000000000000000000000000000000),((83889925846278758599022443:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((3502244307:ℚ)/5000000000),((223395047:ℚ)/312500000),((-1023765329:ℚ)/3337500000),((-6026732921:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((797004363:ℚ)/2000000000),((26452528080767422539933470426662002922252441576414755485423:ℚ)/129485051991320800781250000000000000000000000000000000000000),((19287263529337486704383347:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7064536891:ℚ)/10000000000),((901085727:ℚ)/1250000000),((-4147600089:ℚ)/13468750000),((-12233610673:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3776212683:ℚ)/10000000000),((3689622254800156119806899127627839719736496397153287876204021:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((70378530677270684952247043:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7124573203:ℚ)/10000000000),((3634359169:ℚ)/5000000000),((-16800514183:ℚ)/54350000000),((-12413719609:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1777912729:ℚ)/5000000000),((20577449310993965537415082847135018172563613404928400059393241:ℚ)/100534399592077587890625000000000000000000000000000000000000000),((176117277035614052499707:ℚ)/5120000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7184597867:ℚ)/10000000000),((3664369689:ℚ)/5000000000),((-5670195941:ℚ)/18275000000),((-12593793601:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((332155031:ℚ)/1000000000),((55581375743083567338781934192991985814233640992265332644107:ℚ)/271290122249316406250000000000000000000000000000000000000000),((56748455507748255770957667:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7244611189:ℚ)/10000000000),((3724374103:ℚ)/5000000000),((-17430618721:ℚ)/55300000000),((-12773833567:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((767550831:ℚ)/2500000000),((2531384046114502274044306070926912057226669334858810832363:ℚ)/12230448693750000000000000000000000000000000000000000000000),((49888869165218544768006563:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((920575623:ℚ)/1250000000),((302748583:ℚ)/400000000),((-1428040081:ℚ)/4500000000),((-1641726869:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2495365723:ℚ)/10000000000),((2414761146256731794104821424967478031665984048046689776189:ℚ)/11646344531250000000000000000000000000000000000000000000000),((563758065494730451678987:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((3742278417:ℚ)/5000000000),((1609639177:ℚ)/2000000000),((-7811474239:ℚ)/22880000000),((-6746835251:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1745193531:ℚ)/10000000000),((45664541933145294421872421813500761837416256030771762697433:ℚ)/208914705542400000000000000000000000000000000000000000000000),((5538288260619180442066267:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((3981992359:ℚ)/5000000000),((4263572509:ℚ)/5000000000),((-21205007563:ℚ)/61000000000),((-7465977077:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((510584292921285595204386003191363852870118964750782684367183:ℚ)/2326909907812500000000000000000000000000000000000000000000000),((597809:ℚ)/128000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8442886847:ℚ)/10000000000),((5219577873:ℚ)/5000000000),((-1033223893:ℚ)/2400000000),((-16368660541:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4166931399837007386716623383420972200502833809153771:ℚ)/16200000000000000000000000000000000000000000000000000),((597809:ℚ)/128000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((517737751:ℚ)/500000000),((7126600469:ℚ)/5000000000),((-41246203283:ℚ)/80000000000),((-1105213253:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4614161581232691692341411:ℚ)/15235200000000000000000000),((597809:ℚ)/128000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC10
#check @N11Formalization.C450Source29GroupedC10.bound
#print axioms N11Formalization.C450Source29GroupedC10.valid0
#print axioms N11Formalization.C450Source29GroupedC10.valid1
#print axioms N11Formalization.C450Source29GroupedC10.valid2
#print axioms N11Formalization.C450Source29GroupedC10.valid3
#print axioms N11Formalization.C450Source29GroupedC10.valid4
#print axioms N11Formalization.C450Source29GroupedC10.valid5
#print axioms N11Formalization.C450Source29GroupedC10.valid6
#print axioms N11Formalization.C450Source29GroupedC10.valid7
#print axioms N11Formalization.C450Source29GroupedC10.valid8
#print axioms N11Formalization.C450Source29GroupedC10.valid9
#print axioms N11Formalization.C450Source29GroupedC10.valid10
#print axioms N11Formalization.C450Source29GroupedC10.valid11
#print axioms N11Formalization.C450Source29GroupedC10.valid12
#print axioms N11Formalization.C450Source29GroupedC10.valid13
#print axioms N11Formalization.C450Source29GroupedC10.valid14
#print axioms N11Formalization.C450Source29GroupedC10.bound
#print axioms N11Formalization.C450Source29GroupedC10.endpoint_checks
